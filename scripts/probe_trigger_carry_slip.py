"""One held background hop per auxiliary tour defeats a fixed external alias.

At each external stimulus return the *current* aligned hub latch exactly
once. The stimulus also steps a second active petal cursor once. Its marked
arrival at a distinguished hub rail produces one carry per full auxiliary
tour M; no period/weights supplied to this contact. The main device normally
takes h physical hops per positive, fixed inter-stimulus interval. Gate ONE
background tick for each carry. No event is rejected; a hold is elapsed time,
not a physical hop. On the aligned main orbit of period T, every M-stimulus
subsequence advances by M*h-1 modulo T. It visits every phase iff
gcd(M*h-1,T)=1. This holds for every positive h iff every prime dividing T
divides M (if p does not divide M take h inverse to M modulo p). M=T from
an active clone suffices without knowing either h or target counts. Bad gcd
need not spoil every coarse label histogram. The algebraic pulse map is a
permutation, which does not imply that the whole installed apparatus is.

A hub-only passive observer cannot stall a remote cursor. The new apparatus
explicitly imports two clock-enable distribution trees, not part of the
original petals. The first distributes the stimulus to the reference walker.
The second distributes the resulting reference-hub carry to the main walker.
Each tick each binary relay copies its previous bit to its two child
registers. All scatter vertices receive a dedicated equal-depth leaf. Only
the pulse at the occupied vertex reads its own arriving enable. Identical
wire delays move the carry within the M-interval block but do not change the
net phase slip. Startup labels before pipeline fill are delivered and counted
separately, not selected by outcome. Equal hop rates, synchronized background
updates, stable packets, a jointly aligned main latch and an active reference
are inputs; no microscopic realization or reversibility of the fanout, pulse
source or preparation is inferred. A passive h-clock and a phase-dependent
nonconstant drive are separate countercontrols. No iid or first-shot law.

Run: python3 -B -O -m scripts.probe_trigger_carry_slip
"""

from collections import Counter
from math import gcd

from scripts.probe_bipartite_triangle_origin import need
from scripts.probe_internal_detector_clocks import advance
from scripts.probe_reversible_excitation_detector import Apparatus


class EnableTree:
    """Pipelined fanout: child j and child j+width each read parent j."""

    def __init__(self, vertices):
        self.depth = (vertices - 1).bit_length()
        self.levels = [0] * (self.depth + 1)
        self.widths = [1 << level for level in range(self.depth)]

    def tick(self, command, vertex):
        # Read old local leaf first, then update ALL levels from old parents.
        held = (self.levels[-1] >> vertex) & 1
        for j in range(self.depth, 0, -1):
            bits = self.levels[j - 1]
            self.levels[j] = bits | (bits << self.widths[j - 1])
        self.levels[0] = int(command)
        return held

    def audit(self, vertices):
        latency = self.depth + 1
        for v in range(vertices):
            copy = EnableTree(vertices)
            seen = [copy.tick(t == 0, v) for t in range(latency + 2)]
            need(seen == [0] * latency + [1, 0], "unequal relay delay")
        return latency


def contact(g, state):
    # At the local hub, read only the current incident port. Both directions
    # reach this marked rail once on an active tour; a trapped cursor need not.
    return state[1] == 0 and g.arc[state[:2]] == (g.order[0], 1)


class Driven:
    def __init__(self, main, ref, x, y, label):
        self.g, self.ref = main, ref
        self.x, self.y, self.label = x, y, label
        self.tree = EnableTree(len(main.adj))
        self.trigger = EnableTree(len(ref.adj))
        self.issued = self.elapsed = self.held = self.ref_hops = 0

    def stimulus(self, h):
        need(h >= 1, "positive interval required")
        answer = self.label  # sampled before this interval, never overwritten
        self.issued += 1
        for tick in range(h):
            self.elapsed += 1
            ref_enable = self.trigger.tick(tick == 0, self.y[1])
            carry = ref_enable and contact(self.ref, self.y)
            if ref_enable:
                self.y = self.ref.step(self.y)
                self.ref_hops += 1
            if self.tree.tick(carry, self.x[1]):
                self.held += 1
            else:
                self.x, self.label = advance(self.g, self.x, self.label)
        return answer

    def state(self):
        return (
            self.x,
            self.label,
            self.y,
            tuple(self.tree.levels),
            tuple(self.trigger.levels),
        )


def rotate(g, x, n):
    for _ in range(n):
        x = g.step(x)
    return x


def orbit(g, start):
    state, length = start, 0
    while True:
        state = g.step(state)
        length += 1
        if state == start:
            return length
        need(length < 10000, "fixture orbit did not close")


def max_gap(times, period):
    return max(
        b - a for a, b in zip(times, [*times[1:], times[0] + period], strict=True)
    )


def actual(g, ref, h, shift, direction):
    first = g.order[-1]
    target = g.launch(first, direction, 0)
    x = rotate(g, target, shift)
    y0 = ref.launch(ref.order[0], -direction, 0)
    y = rotate(ref, y0, 3 * shift + 1)
    T, M = orbit(g, x), orbit(ref, y)
    d = gcd(M * h - 1, T)
    drive = Driven(g, ref, x, y, g.arc[x[:2]][0])
    delay = drive.tree.depth + drive.trigger.depth + 2
    warmup = (delay + h - 1) // h
    warm_counts = Counter(drive.stimulus(h) for _ in range(warmup))
    need(sum(warm_counts.values()) == warmup, "lost pipeline-startup answer")
    base = drive.state()
    old_holds, old_ticks, old_ref = drive.held, drive.elapsed, drive.ref_hops
    counts, pairs, seen = Counter(), set(), Counter()
    fine_times, rare_times = [], []
    size = M * T // d
    for t in range(size):
        x, y = drive.x, drive.y
        pairs.add((x, y))  # audit only, not scheduler input
        seen[x] += 1
        if x == target:
            fine_times.append(t)
        answer = drive.stimulus(h)
        counts[answer] += 1
        need(answer == g.arc[x[:2]][0], "local latch lost alignment")
        if answer == 1:
            rare_times.append(t)
    need(drive.state() == base and len(pairs) == size, "wrong joint recurrent period")
    need(
        drive.held - old_holds == size // M
        and drive.elapsed - old_ticks == size * h
        and drive.ref_hops - old_ref == size,
        "carry or elapsed time disappeared",
    )
    need(
        drive.issued
        == warmup + size
        == sum(warm_counts.values()) + sum(counts.values()),
        "did not answer exactly once per stimulus",
    )
    if d == 1:
        need(len(seen) == T and set(seen.values()) == {M}, "full phase coverage")
        need(
            all(counts[i] == M * g.perimeter[i] * g.sizes[i] for i in g.order),
            "wrong active frequencies",
        )
    if h == T == M and g.sizes == (2, 1, 3):
        need(
            max_gap(fine_times, size) == M * (T - 1) + 1 == 3081
            and max_gap(rare_times, size) == M * (T - 4) + 1 == 2913,
            "resonant rare-response latency",
        )
    return counts, size


def arithmetic():
    cases = 0
    for T in range(1, 17):
        for M in range(1, 17):
            for h in range(1, T + 1):
                d = gcd(M * h - 1, T)
                x = y = 0
                seen = set()
                while (x, y) not in seen:
                    seen.add((x, y))
                    x = (x + h - int(y == M - 1)) % T
                    y = (y + 1) % M
                need(
                    (x, y) == (0, 0)
                    and len(seen) == M * T // d
                    and (len(seen) == M * T) == (d == 1),
                    "carry skew period",
                )
                cases += 1
            # gcd test in h repeats modulo T, not just a short-prefix scan.
            p_factors = (
                p
                for p in range(2, T + 1)
                if T % p == 0 and all(p % k for k in range(2, p))
            )
            need(
                all(M % p == 0 for p in p_factors)
                == all(gcd(M * h - 1, T) == 1 for h in range(1, T + 1)),
                "universal stride criterion",
            )
    return cases


def controls(g):
    # Nonconstant, preprogrammed gap T+1 on carry and T otherwise. For a
    # zero-lag command it freezes stroboscopic phase. With a delayed physical
    # gate it also freezes here since the delay is shorter than a single gap.
    x, y = g.launch(0, 1, 0), g.launch(1, 1, 0)
    T = orbit(g, x)
    adaptive = Driven(g, g, x, y, 0)
    predetermined = []
    for _ in range(T):
        predetermined.append(T + int(contact(g, y)))
        y = g.step(y)
    answers = [adaptive.stimulus(h) for h in predetermined]
    need(
        answers == [0] * T and adaptive.x == x and adaptive.held == 1,
        "variable-cadence control",
    )
    # Trapped auxiliary with no mark on its travelling lane or local rail:
    # no carry. Trapped main stays on one physical rail despite regular carries.
    parked = (0, g.starts[0, 1, 0], g.cellmask[2] & -g.cellmask[2])
    inactive_ref = Driven(g, g, x, parked, 0)
    need(
        all(inactive_ref.stimulus(T) == 0 for _ in range(2 * T))
        and inactive_ref.held == 0,
        "trapped reference unexpectedly released a slip",
    )
    inactive_main = Driven(g, g, parked, x, 0)
    need(
        all(inactive_main.stimulus(1) == 0 for _ in range(2 * T))
        and inactive_main.held > 0,
        "drive manufactured an active main sector",
    )
    # A passive strobe on an active file also locks to one phase at h=T.
    need(rotate(g, x, T) == x, "passive resonance control")


def main():
    g = Apparatus((2, 1, 3))
    delay = EnableTree(len(g.adj)).audit(len(g.adj))
    cases = arithmetic()
    for h, shift, direction in ((1, 0, 1), (10, 5, -1), (56, 9, 1), (57, 11, -1)):
        counts, size = actual(g, g, h, shift, direction)
        need(
            size == 3136 and counts == {0: 896, 1: 224, 2: 2016},
            "reference clone histograms",
        )
    # A 4-tick active reference against 56 phases and h=2 gives stride 7:
    # even the coarse rare-rail probability 1/14 cannot be exact in 32 draws.
    wrong, size = actual(g, Apparatus((1,)), 2, 5, 1)
    need(size == 32 and wrong[1] * 14 != size, "mismatched-reference counterexample")
    controls(g)
    print(
        f"{cases} bounded stride checks; two distribution trees at {delay} ticks each; startup answered"
    )
    print("fixed h=1,10,56,57: 3136/3136 labels 896/224/2016; no phase averaging")
    print(
        "h=56 cyclic inter-response gaps: rare phase 3081, rare rail 2913 stimuli; 1 answer each"
    )
    print(
        "wrong reference, trapped marker and preprogrammed nonconstant spacing need not preserve stock"
    )


if __name__ == "__main__":
    main()
