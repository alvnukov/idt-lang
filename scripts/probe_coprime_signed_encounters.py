"""Two supplied raw-occurrence rings; signed meetings, then a local debt counter.

Advance both heads once per tick. One ring holds the L signed occurrences;
the other holds the SAME raw occurrences and one idle cell. Coprimality makes
every pair of positions meet once in L(L+1) ticks, from any starting phases.
This IS a temporal traversal of a Cartesian product, not a derivation of
independent copies, an iid draw or a speed-up. No pair list (raw or survivor),
survivor identities, squared weights, or pre-cancellation enter the detector.
On rail i the signed meeting net is (#plus - #minus)^2 by distributivity.

On a negative meeting add one debt; a positive pays one old debt or emits one
click. For a period of signed meetings x with q=sum x >= 0, the end-debt map
is F(d)=max(d-q,H), H=max(0, suffix sums of -x). This follows by composing
d'=max(0,d-x). At zero initial debt F(0)=H and F(H)=H. Debt conservation then
gives exactly q clicks per subsequent aligned period. First-period candidates
are q+H and may click on a dark rail: suppress the ENTIRE priming period,
counting its cost. Nonnegative net is essential. Darkness gives NO service.

All null, negative, repayment, withheld and delivered ticks are counted.
Each fixed-time trigger does NOT necessarily click. After priming, a serial
queue with one waiting request can instead serve the next request at the
next click; the realized mean inter-completion time is T/(sum q), counting
cyclic gaps. This is not random-arrival latency, fair sampling, absorption of
every fixed-time trial, or a prediction of an iid one-shot detector. Inputs
must repeat unchanged; resetting/repriming is a preparation cost. Strides,
the idle marker, same-rail and relative-role comparators, coherent duplication
and local integer debt storage are supplied. With p plus and m minus entries
on a rail, it has 2*p*m negative meetings per period. Every aligned post-prime
debt is a maximum suffix deficit bounded by this number; no unlimited
capacity is asserted for arbitrary input sizes or unmatched phase frames.

Contrast: unsigned_pair_tickets transports an already addressed ticket;
rotor_event_stream cycles seeds on addressed routes; unary_first_passage uses
already cancelled lengths and scores every hop. Here uncancelled raw pairs
meet one at a time and many ticks are silent. This is an executable finite
alternative, not a reconstructed universal detector.

Run: python3 -B -O -m scripts.probe_coprime_signed_encounters
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd, lcm

from scripts.probe_bipartite_triangle_origin import (
    independent,
    need,
    path_parity,
    reflection,
    seed,
    split,
)


class Rings:
    def __init__(self, first, second, phase=(0, 0), debt=None, strides=(1, 1)):
        self.a, self.b = tuple(first), tuple(second)
        need(self.a and self.b, "empty ring has no circulating cursor")
        for cell in (*self.a, *self.b):
            need(cell is None or cell[1] in (-1, 1), "invalid sign")
        self.p, self.r = phase[0] % len(self.a), phase[1] % len(self.b)
        self.step_a, self.step_b = strides
        self.debt = Counter(debt or {})
        need(all(d >= 0 for d in self.debt.values()), "negative initial debt")

    def tick(self, silent):
        a, b = self.a[self.p], self.b[self.r]
        self.p = (self.p + self.step_a) % len(self.a)
        self.r = (self.r + self.step_b) % len(self.b)
        if a is None or b is None:
            return "idle", None
        rail, sign = a
        if rail != b[0]:
            return "cross", None
        if sign != b[1]:
            self.debt[rail] += 1
            return "negative", rail
        if self.debt[rail]:
            self.debt[rail] -= 1
            return "repaid", rail
        return ("withheld" if silent else "click"), rail

    def period(self, silent=False):
        origin = self.p, self.r
        log = Record()
        log.peak = self.debt.copy()
        while True:
            kind, rail = self.tick(silent)
            log.add(kind, rail)
            if kind == "negative":
                log.peak[rail] = max(log.peak[rail], self.debt[rail])
            if (self.p, self.r) == origin:
                break
        bound = lcm(
            len(self.a) // gcd(len(self.a), self.step_a),
            len(self.b) // gcd(len(self.b), self.step_b),
        )
        need(log.ticks == bound == sum(log.kinds.values()), "lost a clock tick")
        return log


class Record:
    def __init__(self):
        self.kinds, self.clicks, self.withheld = Counter(), Counter(), Counter()
        self.net = Counter()
        self.ticks = self.first = self.last = self.gaps = 0

    def add(self, kind, rail):
        self.ticks += 1
        self.kinds[kind] += 1
        if kind in ("negative", "repaid", "withheld", "click"):
            self.net[rail] += -1 if kind == "negative" else 1
        if kind == "withheld":
            self.withheld[rail] += 1
        if kind == "click":
            self.clicks[rail] += 1
            if self.first:
                self.gaps += self.ticks - self.last
            else:
                self.first = self.ticks
            self.last = self.ticks

    def service(self):
        n = self.kinds["click"]
        if not n:
            return None
        cyclic_sum = self.gaps + self.ticks - self.last + self.first
        need(cyclic_sum == self.ticks, "failed to count all cyclic service gaps")
        return Fraction(cyclic_sum, n)


def installed(word, phase=(0, 0), debt=None):
    return Rings(word, (*word, None), phase, debt)


def stable(word, phase=(0, 0)):
    machine = installed(word, phase)
    prime = machine.period(silent=True)
    anchor = machine.debt.copy()
    log = machine.period()
    need(machine.debt == anchor and not prime.clicks, "invalid silent prime/reset")
    signed = Counter()
    raw_signs = Counter(word)
    for i, sign in word:
        signed[i] += sign
    oracle = Counter({i: z * z for i, z in signed.items()})
    need(
        all(log.peak[i] <= 2 * raw_signs[i, 1] * raw_signs[i, -1] for i in signed),
        "debt exceeded one period's raw negative meetings",
    )
    need(
        log.net == log.clicks == oracle and prime.net == oracle, "signed net or clicks"
    )
    need(prime.withheld == oracle + anchor, "warmup excess/debt")
    need(log.ticks == len(word) * (len(word) + 1), "incomplete coprime position orbit")
    if sum(oracle.values()):
        need(log.service() == Fraction(log.ticks, sum(oracle.values())), "unpaid time")
    else:
        need(log.service() is None, "all-dark service")
    return prime, log


def debt_controls():
    dark = ((0, 1), (0, -1))
    prime, log = stable(dark)
    need(
        prime.withheld == {0: 2} and not log.clicks and prime.ticks == log.ticks == 6,
        "dark startup false clicks",
    )
    old = installed(dark)
    old.period(silent=True)
    new = installed(((0, 1),), debt=old.debt)
    need(
        [new.period().kinds["click"] for _ in range(3)] == [0, 0, 1],
        "stale debt falsely assumed harmless",
    )
    # Equal periods probe ONLY an offset correlation; extra idle cells are not
    # interchangeable with coprimality. Odd L with two pads still is coprime.
    need(
        Rings(dark, dark).period().net[0] == 2
        and Rings(dark, dark, (0, 1)).period().net[0] == -2,
        "equal-length lockstep",
    )
    pad = (*dark, None, None)
    need(
        [Rings(dark, pad, (0, p)).period().net[0] for p in (0, 1)] == [2, -2],
        "noncoprime padded rings",
    )
    bright = ((0, 1), (0, 1), (0, -1))
    need(
        Rings(bright, (*bright, None, None)).period().net[0] == 1, "coprime double pad"
    )
    slipped = Rings(dark, (*dark, None), strides=(2, 1))
    need(slipped.period().ticks == 3, "frozen first head not detected")
    forgotten = tuple((i, 1) for i, _ in dark)
    need(
        stable(forgotten)[1].clicks == {0: 4},
        "forgetting sign leaves raw unsigned stock",
    )
    backward_frame = (*((i, -s) for i, s in bright), None)
    bad = Rings(bright, backward_frame)
    first, second = bad.period(), bad.period()
    need(
        first.net[0] == second.net[0] == -1 and bad.debt[0] >= 2,
        "unmatched parity frames did not invalidate nonnegative-net assumption",
    )
    # Same signed stock, different timing: more raw incidences take longer.
    v = ((0, 1), (0, 1), (1, 1), (2, -1), (2, -1), (2, -1))
    _, base = stable(v)
    _, noisy = stable((*v, (0, 1), (0, -1)))
    need(
        base.clicks == noisy.clicks == {0: 4, 1: 1, 2: 9}
        and (base.service(), noisy.service()) == (Fraction(3), Fraction(36, 7)),
        "raw cost control",
    )
    second_order = Rings(v, (None, *reversed(v)), (4, 5))
    second_order.period(silent=True)
    need(second_order.period().clicks == base.clicks, "separate raw serializations")


def cells(g, label, root=0):
    # Use one parity frame for BOTH streams. Here a per-branch frame suffices
    # because distinct registered branches never share detector addresses.
    parity = path_parity(g, root)
    return [(label(tag), 1 if parity[u] == 0 else -1) for u, tag in enumerate(g.tags)]


def native():
    for k, expected, tally in ((0, (0, 8), (48, 4)), (1, (6, 2), (52, 2))):
        branches = split(seed(0), lambda x, k=k: reflection(k, x))
        for root in range(4):
            word = [
                w
                for b, g in enumerate(branches)
                for w in cells(g, lambda tag, b=b: (b, tag), root)
            ]
            prime, log = stable(word, (3, 5))
            hits = tuple(
                sum(n for (s, _), n in log.clicks.items() if s == b) for b in (0, 1)
            )
            need(
                hits == expected
                and log.ticks == prime.ticks == 72
                and log.service() == 9,
                "triangle interference or issued-tick denominator",
            )
            need(
                (log.kinds["cross"], log.kinds["negative"]) == tally
                and log.kinds["idle"] == 8
                and log.kinds["negative"] == log.kinds["repaid"],
                "lost null/negative/repayment triangle ticks",
            )
    # All heralds, both devices' actual output ports and both rail sublabels
    # encounter one another on the SAME clock. Nothing is discarded in advance.
    for right, anti in ((0, (0, 48, 48, 0)), (1, (36, 12, 12, 36))):
        product_g = independent(seed(0), seed(1))
        word = []
        for herald, h in enumerate(split(product_g, lambda t: (t[1], t[0]))):
            for a, p in enumerate(split(h, lambda t: (reflection(0, t[0]), t[1]))):
                for b, g in enumerate(
                    split(p, lambda t, right=right: (t[0], reflection(right, t[1])))
                ):
                    word.extend(cells(g, lambda t, prefix=(herald, a, b): (*prefix, t)))
        _, log = stable(word)
        table = Counter()
        for (h, a, b, _), n in log.clicks.items():
            table[h, a, b] += n
        need(
            tuple(table[1, a, b] for a, b in product(range(2), repeat=2)) == anti
            and sum(table.values()) == 256
            and log.ticks == 65792
            and log.service() == 257,
            "all-issued joint triangle",
        )


def main():
    cases = 0
    for length in range(1, 5):
        for word in product(((0, 1), (0, -1), (1, 1), (1, -1)), repeat=length):
            for phase in product(range(length), range(length + 1)):
                stable(word, phase)
                cases += 1
    debt_controls()
    native()
    print(f"{cases} raw input/phase cases; one accounted silent period before service")
    print(
        "triangle fixed ticks: 8/72 clicks (0:8 or 6:2); 64 null/debt ticks, mean gap 9"
    )
    print(
        "joint unconditioned 256/65792; anti-herald 0/48/48/0 or 36/12/12/36; mean gap 257"
    )
    print(
        "two raw occurrence streams, coherent relative roles and signed debt; not a lossless fixed-time detector"
    )


if __name__ == "__main__":
    main()
