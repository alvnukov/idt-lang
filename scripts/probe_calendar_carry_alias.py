"""What survives a fixed, repeating external calendar of positive gap lengths?

This extends the *installed* active two-tree carry detector, not its physics.
The P distinguished calendar slots repeat, the gaps sum to H, the auxiliary
emits once in M delivered hops, and the aligned main circle has T phases.
Write g = gcd(P,M). After pipeline fill, L = lcm(P,M) stimuli restore the
calendar and auxiliary schedule. They supply (M/g)*H background ticks and
exactly P/g holds. At any fixed residue of this L-slot block the sampled
main phase thus advances D = (M/g)*H - P/g modulo T. It covers all T phases
at that residue iff gcd(D,T)=1. A full sweep at each residue gives the
active square shares; its failure alone says nothing decisive about coarse
label counts pooled across residues.

For M=T, every positive gap word of a specified length P gives a full sweep
at each fixed residue iff v_p(P) < v_p(T) for every prime p dividing T.
Indeed, in that case p divides T/g but not P/g. Otherwise T/g is a unit
at an offending p. Choose H >= P+1 with (T/g)*H = P/g modulo p, realizable
by positive gaps (1,...,1,H-P+1). This theorem is about a stated calendar
and reference residue, not a necessary condition for any coarser readout.
In particular P=2 works for every canonical petal clone (4 divides T).

Both gap words below are fixed before, and independent of, marker phase.
No event is rejected, and cold-start answers are counted separately. All
counts are deterministic return-cycle frequencies; no phase distribution,
one-shot or iid law, or assertion about aperiodic drives is made.

Run: python3 -B -O -m scripts.probe_calendar_carry_alias
"""

from collections import Counter
from itertools import product
from math import gcd, lcm

from scripts.probe_bipartite_triangle_origin import need
from scripts.probe_internal_detector_clocks import factors
from scripts.probe_reversible_excitation_detector import Apparatus
from scripts.probe_trigger_carry_slip import Driven, orbit, rotate


def schedule(T, M, gaps):
    need(T > 0 and M > 0 and gaps and all(h >= 1 for h in gaps),
         "positive orbit sizes and calendar gaps required")
    P = len(gaps)
    g = gcd(P, M)
    stride = (M // g) * sum(gaps) - P // g
    return lcm(P, M), stride, gcd(stride, T)


def counterword(T, P):
    """A positive P-slot word with a bad fixed-residue stride, if one exists."""
    g = gcd(P, T)
    for p in factors(T):
        if (T // g) % p:
            base = P + 1
            residue = (P // g) * pow(T // g, -1, p) % p
            H = base + (residue - base) % p
            return (1,) * (P - 1) + (H - P + 1,)
    return None


def residue_checks():
    """Compare independent one-step enumeration with the full-block stride."""
    cases = 0
    for T, M in product(range(1, 10), repeat=2):
        for P in range(1, 5):
            for gaps in product((1, 2), repeat=P):
                L, stride, d = schedule(T, M, gaps)
                x = y = 0
                visits = [set() for _ in range(L)]
                for t in range(L * (T // d)):
                    visits[t % L].add(x)
                    x = (x + gaps[t % P] - int(y == M - 1)) % T
                    y = (y + 1) % M
                    if (t + 1) % L == 0:
                        need(y == 0 and x == ((t + 1) // L * stride) % T,
                             "one-step schedule disagrees with macro stride")
                need(x == y == 0 and all(len(v) == T // d for v in visits),
                     "wrong fixed-residue phase coverage")
                cases += 1
    return cases


def universal_checks():
    cases = 0
    for T in range(1, 49):
        for P in range(1, 37):
            g = gcd(P, T)
            # Positive P-slot gap totals represent each residue of H mod T.
            bounded_oracle = all(
                gcd((T // g) * H - P // g, T) == 1 for H in range(P, P + T)
            )
            word = counterword(T, P)
            need((word is None) == bounded_oracle, "incorrect P-slot classifier")
            if word is not None:
                need(len(word) == P and min(word) >= 1 and word[-1] > 1
                     and schedule(T, T, word)[2] > 1, "invalid calendar witness")
            if P == 2 and T % 4 == 0:
                need(bounded_oracle, "alternating positive gaps should be safe here")
            cases += 1
    return cases


def delayed_orbit(g, gaps, x, y, T, M):
    """Read actual leaf-delayed pulses; macro arithmetic never drives the device."""
    P = len(gaps)
    L, stride, d = schedule(T, M, gaps)
    f = Driven(g, g, x, y, g.arc[x[:2]][0])
    # Advance whole calendars until the last cold-start command could have
    # crossed both pipelines. Keep every startup answer in a separate record.
    latency = f.trigger.depth + f.tree.depth + 2
    startup = Counter()
    while f.elapsed < latency:
        for gap in gaps:
            startup[f.stimulus(gap)] += 1
    need(sum(startup.values()) == f.issued, "lost a startup response")
    origin = f.state()
    initial_ticks, initial_ref, initial_held = f.elapsed, f.ref_hops, f.held
    by_slot = [set() for _ in range(L)]
    labels = Counter()
    size = L * (T // d)
    for n in range(size):
        if n % L == 0:
            block_start = f.x
        before = f.x
        by_slot[n % L].add(before)
        answer = f.stimulus(gaps[n % P])
        need(answer == g.arc[before[:2]][0], "misaligned physical answer")
        labels[answer] += 1
        if (n + 1) % L == 0:
            need(f.x == rotate(g, block_start, stride % T),
                 "delayed holds changed the macro stride")
            need((f.state() == origin) == (n + 1 == size),
                 "incorrect return at fixed calendar and reference residue")
    need(all(len(s) == T // d for s in by_slot), "wrong physical phase coverage")
    need(f.issued == sum(startup.values()) + size
         and sum(labels.values()) == size and f.ref_hops - initial_ref == size
         and f.held - initial_held == size // M
         and f.elapsed - initial_ticks == size // P * sum(gaps),
         "lost an issued answer, delayed pulse, hold or elapsed clock tick")
    return tuple(labels[i] for i in g.order)


def physical():
    g = Apparatus((1, 1))  # canonical neutral packet (+1,-1); bypass signed installation
    words = ((1, 2), (1, 1, 1, 1, 1, 1, 1, 2))
    expected = ({(32, 32)}, {(3, 5), (4, 4), (5, 3)})
    total = 0
    for word, allowed in zip(words, expected, strict=True):
        for main_direction, ref_direction in product((-1, 1), repeat=2):
            main = g.launch(0, main_direction, 0)
            ref = g.launch(0, ref_direction, 0)
            T, M = orbit(g, main), orbit(g, ref)
            need(T == M == 8, "canonical two-rail clone changed")
            observed = set()
            for a, b in product(range(T), range(M)):
                row = delayed_orbit(g, word, rotate(g, main, a), rotate(g, ref, b), T, M)
                observed.add(row)
                total += 1
            need(observed == allowed, "unexpected coarse histogram set")
    return total


def main():
    print(f"{residue_checks()} gap/period checks; {universal_checks()} clone classifiers")
    print(f"{physical()} delayed all-phase runs (64 per orientation pair and calendar)")
    print("alternating gaps (1,2): 32/32; seven 1s then 2: 3/5, 4/4 or 5/3")
    print("same fixed 8-slot drive can preserve or spoil coarse shares; no phase averaging")


if __name__ == "__main__":
    main()
