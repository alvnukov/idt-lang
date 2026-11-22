"""Square frequencies from local first passages, conditional on a fixed packet.

Compare signed occurrences on each named rail and cancel them into a unary
chain of anonymous apparatus cells. These cells are NOT surviving input
addresses. One persistent cursor takes one hop for each issued trigger and
prints the current rail. At the root it goes towards the exit; each interior
switch alternates towards the root / towards the exit. On arrival at the exit a
control link moves the cursor to the next nonempty rail's root without changing
switches. Rail order affects time correlations, not complete-block counts.
No pair domain, random seed, target probabilities or stock-weighted scheduler.

If every interior switch initially faces the root, the first-passage length
is n² on a chain of n edges. More generally let b_j mark an initially
exit-facing switch at position j (1 <= j < n). The passage terminates: in an
infinite walk some vertex is visited infinitely often, hence its right neighbor
also is, all the way to the exit. The last departure from each interior vertex
is rightward, so its *next* departure afterwards is leftward. Write R_i for
right crossings of edge i, numbered from 0. Left crossings are R_i-1, since the
cursor starts on the left and ends on the right. R_(n-1)=1, and alternation
at vertex j gives R_(j-1)=R_j+1-b_j. Thus the number of hops is
sum_i (2 R_i-1) = n² - 2 sum_j j b_j. Every later passage has length n².

Supplied: a coherent signed stream, or relative path parity on each connected
bipartite packet, a serial port collector and end-of-preparation boundary,
opposite-role cancellation, a mutable directed root/exit apparatus, a fixed
cyclic wiring and one persistent trigger-driven cursor. Bypass/control transfers
have no detector label and require no additional input trigger; this is not an
equal-physical-time law. One fresh trigger advances the detector for a *fixed*
prepared pattern: this is neither independent clicks on arbitrary changing
unknown particles, nor a microscopic energy/absorption theorem, nor Bell-local
selection. A completely dark packet cannot accept triggers in this model.
Run: python3 -B -O -m scripts.probe_unary_first_passage_detector
"""

from collections import Counter
from dataclasses import dataclass, field
from itertools import product

from scripts.probe_bipartite_triangle_origin import (
    D,
    need,
    path_parity,
    reflection,
    rename,
    seed,
    split,
)


@dataclass
class Chain:
    # One bit per unit; the root's bit is unused. Consecutive cells are joined.
    right: list[bool] = field(default_factory=list)
    head: int = 0

    def hop(self):
        j = self.head
        if j == 0:
            self.head = 1
        else:
            self.head += 1 if self.right[j] else -1
            self.right[j] = not self.right[j]
        if self.head == len(self.right):
            self.head = 0  # Exit control link; not a reverse walk over switches.
            return True
        return False


class NoLiveRail(ValueError):
    """A null packet supplies no channel; refusal is not a successful hit."""


class Detector:
    def __init__(self, port_count, events):
        need(port_count > 0, "no installed ports")
        self.chains = [Chain() for _ in range(port_count)]
        roles = [0] * port_count
        for rail, sign in events:
            need(0 <= rail < port_count and sign in (-1, 1), "invalid occurrence")
            cells = self.chains[rail].right
            if not cells or roles[rail] == sign:
                roles[rail] = sign
                cells.append(False)
            else:
                cells.pop()
        self.first = self.rail = self.next_live(-1)

    def next_live(self, after):
        for step in range(1, len(self.chains) + 1):
            i = (after + step) % len(self.chains)
            if self.chains[i].right:
                return i
        raise NoLiveRail("every rail is dark")

    def issue(self):
        """Exactly one labelled hop; the Boolean is only a boundary monitor."""
        port = self.rail
        done = self.chains[port].hop()
        if done:
            self.rail = self.next_live(port)
        return port, done and self.rail == self.first


def census(detector, cap=10000):
    # Test monitor: stop on the observed wrap, not an oracle-supplied period.
    counts = Counter()
    for _ in range(cap):
        port, wrapped = detector.issue()
        counts[port] += 1
        if wrapped:
            return tuple(counts[j] for j in range(len(detector.chains)))
    raise AssertionError("no wrap within test budget")


def raw(v):
    return ((i, 1 if x > 0 else -1) for i, x in enumerate(v) for _ in range(abs(x)))


def graph_events(g, root, offset=0):
    # Graph frame is supplied by parity propagation; this is not a local leader
    # election. Flipping either connected packet's frame leaves its stock alone.
    sides = path_parity(g, root)
    return ((offset + tag, 1 if sides[u] == 0 else -1) for u, tag in enumerate(g.tags))


def exclusive_children(v):
    # Native exclusive instrument's *raw* ten signed paths per occurrence;
    # only gate connectivity appears here, not its reduced matrix or its stock.
    for src, s in raw(v):
        yield 9, s
        for d in D:
            yield 3*d + reflection(d, src), s
            yield 3*d + (src+1) % 3, -s
            yield 3*d + (src+2) % 3, -s


def switches():
    tried = 0
    for n in range(1, 11):
        for bits in product((False, True), repeat=n-1):
            detector = Detector(1, raw((n,)))
            chain = detector.chains[0]
            chain.right[1:] = bits
            first = n*n - 2*sum(j for j, bit in enumerate(bits, 1) if bit)
            need(census(detector) == (first,), "arbitrary launch phase")
            need(chain.head == 0 and not any(chain.right), "not automatically restored")
            need(census(detector) == (n*n,), "next passage did not self-normalize")
            tried += 1
    return tried


def inputs_and_controls():
    nwords = 0
    for length in range(7):
        for events in product(((0, 1), (0, -1), (1, 1), (1, -1)), repeat=length):
            oracle = tuple(sum(s for i, s in events if i == j)**2 for j in range(2))
            if any(oracle):
                need(census(Detector(2, events)) == oracle, "serial quotient/order")
            else:
                try:
                    Detector(2, events)
                except NoLiveRail:
                    pass
                else:
                    raise AssertionError("all-dark packet accepted")
            nwords += 1
    v = (2, 1, -3)
    need(census(Detector(3, raw(v))) == (4, 1, 9), "unscaled neutral rail stock")
    d = Detector(10, exclusive_children(v))
    ports = census(d)
    need(ports == (16,4,4,1,4,1,9,9,36,0), "raw exclusive gate")
    registers = tuple(sum(ports[3*i:3*i+3]) for i in D)
    need(registers == (24, 6, 54) and sum(ports) == 84, "all triggers, no drain")
    need(census(d) == ports, "exclusive period does not repeat")
    # Blank every switch/cursor before each trigger: deterministic first rail
    # every time. Selecting the reset's starting port is not a sampling law.
    firsts = Counter(Detector(3, raw(v)).issue()[0] for _ in range(14))
    need(firsts == {0: 14}, "fresh start control")
    # Retuning between triggers has no per-setting guarantee. Alternating two
    # fresh settings for an integral number of ostensibly adequate samples
    # still gives only their common first label in each conditional sequence.
    alternates = [Counter(), Counter()]
    for k in range(10):
        selector = k % 2
        tuning = ((1,2), (2,1))[selector]
        alternates[selector][Detector(2, raw(tuning)).issue()[0]] += 1
    need(alternates == [{0:5}, {0:5}], "adversarial setting/reset")
    # Arbitrary inputs are legitimate at completed-block boundaries, with an
    # explicitly rebuilt passive apparatus; no continuity across rebuilds.
    for tuning in ((1,2), (2,1), (0,-1), (-2,0)):
        need(census(Detector(2, raw(tuning))) == tuple(x*x for x in tuning),
             "completed-block setting change")
    return nwords, registers


def interference():
    # Two read registers of the frozen unsigned triangle, with rail sublabels.
    g = seed(0)
    one = tuple(graph_events(g, 0))
    both_registers = (*one, *((i+3,s) for i,s in one))
    need(census(Detector(6, both_registers)) == (0,1,1,0,1,1), "one sheet only")
    for dial, oracle in ((0, (0,0,0,0,4,4)), (1, (1,4,1,1,0,1))):
        pos, neg = split(g, lambda i, dial=dial: reflection(dial, i))
        for a, b in product(range(4), repeat=2):
            p = rename(pos, (3,2,1,0))
            events = (*graph_events(p, a), *graph_events(neg, b, 3))
            need(census(Detector(6, reversed(events))) == oracle,
                 "unsigned split, changed frame or arrival order")
        need(sum(oracle) == 8, "unexpected split gain")


def main():
    phases = switches()
    nwords, registers = inputs_and_controls()
    interference()
    print(f"unary first passage: {phases} phase patterns; {nwords} signed input words")
    print(f"native interference: (0,8) or (6,2); exclusive registers {registers}, 84/84 labels")
    print("fixed-pattern periodic clicks only; fresh reset, null input and variable settings bounded")


if __name__ == "__main__":
    main()
